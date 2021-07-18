// Wasmer will let you easily run Wasm module in a Rust host.
//
// This example illustrates the basics of using Wasmer through a "Hello World"-like project:
//
//   1. How to load a Wasm modules as bytes
//   2. How to compile the module
//   3. How to create an instance of the module
//
// You can run the example directly by executing in Wasmer root:
//
// ```shell
// go test examples/example_instance_test.go
// ```
//
// Ready?

package main

import (
	"fmt"
	"io/ioutil"
	"time"

	"github.com/gravitational/acre/pkg/types"
	"github.com/wasmerio/wasmer-go/wasmer"
)

func ExampleInstance() {
	// Let's declare the Wasm module.
	//
	// We are using the text representation of the module here.
	wasmBytes, err := ioutil.ReadFile("target/wasm32-unknown-unknown/debug/acre.wasm")
	if err != nil {
		panic(err)
	}

	// Create an Engine
	engine := wasmer.NewEngine()

	// Create a Store
	store := wasmer.NewStore(engine)

	fmt.Println("Compiling module...")
	module, err := wasmer.NewModule(store, wasmBytes)

	if err != nil {
		fmt.Println("Failed to compile module:", err)
	}

	// Create an empty import object.
	importObject := wasmer.NewImportObject()

	fmt.Println("Instantiating module...")
	// Let's instantiate the Wasm module.
	instance, err := wasmer.NewInstance(module, importObject)

	if err != nil {
		panic(fmt.Sprintln("Failed to instantiate the module:", err))
	}

	// We now have an instance ready to be used.
	//
	// From an `Instance` we can fetch any exported entities from the Wasm module.
	// Each of these entities is covered in others examples.
	//
	// Here we are fetching an exported function. We won't go into details here
	// as the main focus of this example is to show how to create an instance out
	// of a Wasm module and have basic interactions with it.
	add, err := instance.Exports.GetFunction("add")
	if err != nil {
		panic(fmt.Sprintln("Failed to get the `add` function:", err))
	}

	fmt.Println("Calling `add` function...")
	result, err := add(1, 2)

	if err != nil {
		panic(fmt.Sprintln("Failed to call the `add` function:", err))
	}

	fmt.Println("Results of `add`:", result)

	w := wasm{}

	w.alloc, err = instance.Exports.GetFunction("alloc")
	if err != nil {
		panic(err)
	}

	w.setAt, err = instance.Exports.GetFunction("set_at")
	if err != nil {
		panic(err)
	}

	w.getAt, err = instance.Exports.GetFunction("get_at")
	if err != nil {
		panic(err)
	}

	w.call, err = instance.Exports.GetFunction("call")
	if err != nil {
		panic(err)
	}

	start := time.Now()
	iters := 13000
	for i := 0; i < iters; i++ {
		requestResponse(w)
	}
	diff := time.Now().Sub(start)
	fmt.Printf("%v iterations in %v, %v per iteration", iters, diff, diff/time.Duration(iters))

	// Output:
	// Compiling module...
	// Instantiating module...
	// Calling `add_one` function...
	// Results of `add_one`: 2
}

func requestResponse(w wasm) {
	message := &types.Request{
		Message: "Hello, World!",
	}

	responseHeader := &types.ResponseHeader{
		SizeBytes: 4294967295,
		Ptr:       4294967295,
	}

	ptrVal, len := writeMessage(w, message)

	rePtrVal, err := w.call(ptrVal, len)
	if err != nil {
		panic(err)
	}

	data, err := readMessageBytes(w, rePtrVal, responseHeader.Size())
	if err != nil {
		panic(err)
	}

	//fmt.Printf("Data: %#v\n", data)

	if err = responseHeader.Unmarshal(data); err != nil {
		panic(err)
	}

	//	fmt.Printf("Ptr val: %v %v %v\n", ptrVal, rePtrVal, len)
	//	fmt.Printf("Out: %v %v", responseHeader.SizeBytes, responseHeader.Ptr)

	responseData, err := readMessageBytes(w, int32(responseHeader.Ptr), int(responseHeader.SizeBytes))
	if err != nil {
		panic(err)
	}

	var response types.Response
	response.Unmarshal(responseData)
	//fmt.Printf("Response: %#v", response)
}

func demo() {
	/*
				cap := 16
				ptrVal, err := alloc(cap)
				if err != nil {
					panic(err)
				}

				_, err = setAt(ptrVal, 0, 1)
				if err != nil {
					panic(err)
				}

				_, err = setAt(ptrVal, 1, 2)
				if err != nil {
					panic(err)
				}

				b1, err := getAt(ptrVal, 0)
				if err != nil {
					panic(err)
				}

				b2, err := getAt(ptrVal, 1)
				if err != nil {
					panic(err)
				}

		fmt.Printf("%v %v", b1, b2)
	*/

}

type wasm struct {
	alloc func(...interface{}) (interface{}, error)
	setAt func(...interface{}) (interface{}, error)
	getAt func(...interface{}) (interface{}, error)
	call  func(...interface{}) (interface{}, error)
}

// Int64Size is a constant for 64 bit integer byte size
const Int64Size = 8

// Int32Size is a constant for 32 bit integer byte size
const Int32Size = 4

type m interface {
	MarshalTo(dAtA []byte) (int, error)
	Size() (n int)
}

func marshalMessage(msg m) []byte {
	messageSize := msg.Size()
	bytes := make([]byte, messageSize)
	_, err := msg.MarshalTo(bytes)
	if err != nil {
		panic(err)
	}
	return bytes
}

func readMessageBytes(w wasm, ptrVal interface{}, size int) ([]byte, error) {
	data := make([]byte, size, size)
	for i := range data {
		b, err := w.getAt(ptrVal, i)
		if err != nil {
			panic(err)
		}
		data[i] = byte(b.(int32))
	}
	return data, nil
}

func writeMessage(w wasm, msg m) (interface{}, int) {
	data := marshalMessage(msg)

	ptrVal, err := w.alloc(len(data))
	//	fmt.Printf("allocated: %v for data(%v) %#v\n", ptrVal, len(data), data)
	if err != nil {
		panic(err)
	}

	for i, byte := range data {
		_, err = w.setAt(ptrVal, i, int32(byte))
		if err != nil {
			panic(err)
		}
	}

	return ptrVal, len(data)
}

func main() {
	ExampleInstance()
}
