# predicate

## Installing predicate

```bash
poetry install
```

Alternately, `poetry shell` can also be used to run `predicate`.

## Working with policies

See example policies in the [examples/](examples/) folder.

### Testing a policy

```bash
predicate test examples/access.py
```

### Exporting a policy

```bash
predicate export examples/access.py
```
