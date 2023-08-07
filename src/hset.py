from dataclasses import dataclass
from typing import TypeVar, Generic


T = TypeVar("T")


@dataclass
class hSet(Generic[T]):
    hset: list[T]

    def __post_init__(self):
        self.hset = list(set(self.hset))

    def add(self, elem):
        as_set = set(self.hset)
        as_set.add(elem)
        self.hset = list(as_set)

    def remove(self, elem):
        as_set = set(self.hset)
        as_set.remove(elem)
        self.hset = list(as_set)

    def __or__(self, other: 'hSet'):
        as_set = set(self.hset)
        as_set_other = set(other.hset)
        return hSet(list(as_set | as_set_other))

    def __iter__(self):
        return iter(self.hset)
